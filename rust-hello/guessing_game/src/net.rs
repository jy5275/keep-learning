use std::error::Error;
use clap::Parser;
use reqwest::blocking::Client;

#[derive(Parser)]
#[command(
    author,
    version,
    about = "Sends HTTP req and prints detailed info"
)]
struct Cli {
    #[arg(short, long, help = "Target URL", required = true)]
    url: String,
}

fn send_req(url: &str) -> Result<reqwest::blocking::Response, Box<dyn Error>>{
    let client = Client::builder().build()?;
    let resp = client.get(url).send()?;
    Ok(resp)
}

fn print_resp_details(resp: reqwest::blocking::Response) -> Result<(), Box<dyn Error>> {
    println!("Status: {}", resp.status());
    println!("Headers:");
    for (k, v) in resp.headers().iter() {
        println!("  {}: {}", k, v.to_str().unwrap_or("[unprintable]"));
    }
    let body = resp.text()?;
    println!("Body: \n{}", body);
    Ok(())
}

pub fn deep_rust() -> Result<(), Box<dyn Error>>{
    let cli = Cli::parse();
    let resp = send_req(&cli.url)?;

    print_resp_details(resp)?;
    Ok(())
}
