
let statusEnabled: boolean = false;

const Status = {
    output: (msg: string): void => {
        if(statusEnabled) {
            process.stdout.write(msg);
        }
    },
    error: (msg: string): void => {
        if(statusEnabled) {
            process.stderr.write(msg);
        }
    },
    enable: (): void => {
        statusEnabled = true;
    },
    statusDisable: (): void => {
        statusEnabled = false;
    }
};

export { 
    Status 
};
